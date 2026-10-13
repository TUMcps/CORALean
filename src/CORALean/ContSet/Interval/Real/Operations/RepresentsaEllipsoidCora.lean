import CORALean.ContSet.Interval.Real.Operations.Radius

/-!
# `Interval.representsaEllipsoidCora`: the `'ellipsoid'` test as CORA's code computes it

`@interval/representsa_.m`, branch `'ellipsoid'` (l. 92-99), the same test as `'capsule'`
(`Interval.representsaCapsuleCora`), under the comment "either 1D, a point, or at most one
dimension has non-zero width": `n == 1 || isPoint || nnz(withinTol(rad(I),0,tol)) <= 1`, which
counts the zero-width dimensions. Tolerance `0`. Read from the source, not run.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

open Classical in
/-- CORA's `res` for `representsa_(I, 'ellipsoid')`: the same test as `'capsule'`. -/
noncomputable def Interval.representsaEllipsoidCora (I : Interval (Vec ℝ n)) : Bool :=
  let rad := I.radius                                          -- rad(I)
  let isPoint := if ∀ i, rad i = 0 then true else false        -- all(withinTol(rad(I),0,tol))
  let nnzZero := (Finset.univ.filter fun i => rad i = 0).card  -- nnz(withinTol(rad(I),0,tol))
  (if n = 1 then true else false) || isPoint ||                -- n == 1 || isPoint ||
    (if nnzZero ≤ 1 then true else false)                      -- nnz(withinTol(..)) <= 1

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
