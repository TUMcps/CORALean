import CORALean.ContSet.Zonotope.Real.Operations.Mtimes

/-!
# `Zonotope.minkDiffDegenerateCora`, CORA's `minkDiff` at a degenerate minuend

CORA's `@zonotope/minkDiff.m` for a minuend that is not full-dimensional (l. 153), a subtrahend
that is not full-dimensional either (l. 154-159) and generator matrices of equal rank (l. 161):
`[U, S] = svd(generators(minuend))` (l. 166), `newDim` the number of nonzero columns of `S`
(l. 167), `P_minuend = U(1:newDim, :)` (l. 168), the same for the subtrahend (l. 171-173) only to
check that both projections agree (l. 176-177, else an error, l. 188-192), then the difference of
the projected sets in `ℝ^newDim` (l. 179-183) mapped back by `pinv(P_minuend)` (l. 186).

Two slips: `U(1:newDim, :)` takes the first rows of `U` where the range of the generators is
spanned by its first columns, and the projection forgets the component of the minuend's centre
outside that range, which `pinv` cannot bring back: every result lies in the row space of
`P_minuend`, a subspace through the origin, wherever the minuend lies.

One `let` per line of the source. The recursive call is a parameter (any method, any result); the
SVD factor `U` is a parameter that the theorems constrain. The rows of an orthogonal `U` are
orthonormal, so `P_minuend * P_minuendᵀ = I` and `pinv(P_minuend) = P_minuendᵀ`, which is what the
last line uses. Read from the source, not run.

## References

* [1] `contSet/@zonotope/minkDiff.m`, CORA, ll. 113-114, 153-193.
-/

-- Authors:       Claude Opus 5.5
-- Written:       13-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1]'s degenerate branch past its guards: project with the first `newDim` rows of the SVD
factor `U`, take the difference there (`minkDiffRec`), map back with `pinv = ᵀ`. -/
def Zonotope.minkDiffDegenerateCora (minuend subtrahend : Zonotope (Vec ℝ n)) (U : Mat ℝ n n)
    (newDim : ℕ) (hk : newDim ≤ n)
    (minkDiffRec : Zonotope (Vec ℝ newDim) → Zonotope (Vec ℝ newDim) → Zonotope (Vec ℝ newDim)) :
    Zonotope (Vec ℝ n) :=
  -- l. 168: `P_minuend = U(1:newDim, :)`
  let P_minuend : Mat ℝ newDim n := fun i j => U (Fin.castLE hk i) j
  -- l. 179: `minuend_proj = P_minuend * minuend`
  let minuend_proj : Zonotope (Vec ℝ newDim) := minuend.mtimes P_minuend
  -- l. 180: `subtrahend_proj = P_minuend * subtrahend`
  let subtrahend_proj : Zonotope (Vec ℝ newDim) := subtrahend.mtimes P_minuend
  -- l. 183: `Z_proj = minkDiff(minuend_proj, subtrahend_proj, method)`
  let Z_proj : Zonotope (Vec ℝ newDim) := minkDiffRec minuend_proj subtrahend_proj
  -- l. 186: `Z = pinv(P_minuend) * Z_proj`
  Z_proj.mtimes P_minuendᵀ

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
