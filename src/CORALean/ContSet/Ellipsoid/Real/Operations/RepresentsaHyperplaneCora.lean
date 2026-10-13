module

public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid

@[expose] public section

/-!
# `Ellipsoid.representsaHyperplaneCora`: the `'hyperplane'` test as CORA's code computes it

`@ellipsoid/representsa_.m` opens with `representsa_emptyObject` (a set without data, of dimension
zero here, is answered first) and then reads, for `type = 'hyperplane'` (l. 143-146),

```
% ellipsoid cannot be unbounded (unless 1D, where hyperplane also bounded)
res = n == 1;
```

so every one-dimensional set is answered `true`. In one dimension a hyperplane `{x | a x = b}`,
`a ≠ 0`, is a single point; a set of positive length is not. Read from the source, not run.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `res` for `representsa_(ellipsoid, 'hyperplane')`, nonempty object, dimension `n`. -/
def Ellipsoid.representsaHyperplaneCora (_E : Ellipsoid n) : Bool :=
  -- n = dim(ellipsoid)
  let dim := n
  -- res = n == 1
  dim == 1

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
