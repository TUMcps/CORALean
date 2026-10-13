module

public import CORALean.ContSet.ConPolyZono.Real.ConPolyZono

@[expose] public section

/-!
# `ConPolyZono.representsaHyperplaneCora`: the `'hyperplane'` test as CORA's code computes it

`@conPolyZono/representsa_.m` opens with `representsa_emptyObject` (a set without data, of dimension
zero here, is answered first) and then reads, for `type = 'hyperplane'` (l. 82-85),

```
% constrained polynomial zonotopes cannot be unbounded (unless 1D, where hyperplane is also bounded)
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

/-- CORA's `res` for `representsa_(conPolyZono, 'hyperplane')`, nonempty object, dimension `n`. -/
def ConPolyZono.representsaHyperplaneCora (_cPZ : ConPolyZono (Vec ℝ n)) : Bool :=
  -- n = dim(conPolyZono)
  let dim := n
  -- res = n == 1
  dim == 1

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
