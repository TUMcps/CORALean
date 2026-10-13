import CORALean.ContSet.Interval.Real.Operations.Radius

/-!
# `Interval.representsaCapsuleCora`: the `'capsule'` test as CORA's code computes it

`@interval/representsa_.m`, branch `'capsule'` (l. 70-75; `'ellipsoid'`, l. 92-99, is the same
test, `Interval.representsaEllipsoidCora`), under the comment "either 1D, a point, or at most one
dimension has non-zero width":

```
isPoint = all(withinTol(rad(I),0,tol));                                   % l. 53
res = n == 1 || isPoint || nnz(withinTol(rad(I),0,tol)) <= 1;
```

`withinTol(rad(I),0,tol)` is `true` exactly for the dimensions of width **zero**, so the third
disjunct counts the zero-width dimensions and tests them `<= 1`, where "at most one non-zero
width" is `nnz(~withinTol(rad(I),0,tol)) <= 1`. Tolerance `0`. Read from the source, not run.
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
/-- CORA's `res` for `representsa_(I, 'capsule')` (the `n` is `dim(I)`). -/
noncomputable def Interval.representsaCapsuleCora (I : Interval (Vec ℝ n)) : Bool :=
  let rad := I.radius                                          -- rad(I)
  let isPoint := if ∀ i, rad i = 0 then true else false        -- all(withinTol(rad(I),0,tol))
  let nnzZero := (Finset.univ.filter fun i => rad i = 0).card  -- nnz(withinTol(rad(I),0,tol))
  (if n = 1 then true else false) || isPoint ||                -- n == 1 || isPoint ||
    (if nnzZero ≤ 1 then true else false)                      -- nnz(withinTol(..)) <= 1

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
