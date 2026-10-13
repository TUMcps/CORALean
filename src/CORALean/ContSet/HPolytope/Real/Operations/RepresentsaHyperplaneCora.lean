module

public import CORALean.ContSet.HPolytope.Real.HPolytope

@[expose] public section

/-!
# `HPolytope.representsaHyperplaneCora`: the `'hyperplane'` test as CORA's code computes it

`@polytope/representsa_.m` opens with

```
[emptyObj,res] = representsa_emptyObject(P,type);
if emptyObj; return; end
```

and `@polytope/isemptyobject.m` (l. 36) calls an H-representation without inequality and without
equality rows an "empty object" (its comment: "this represents R^n since there are no constraints
excluding any point"). `@contSet/representsa_emptyObject.m` then treats every such object as the
empty set: for `type = 'hyperplane'` it sets `res = true` (l. 68). Otherwise the branch
`'hyperplane'` of `representsa_.m` (l. 259) reads `res = isempty(P.A_.val) && size(P.Ae_.val,1)
== 1`. Read from the source, not run.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `res` for `representsa_(P, 'hyperplane')`, H-representation. -/
def HPolytope.representsaHyperplaneCora (P : HPolytope (Fin n → ℝ)) : Bool :=
  -- emptyObj = isemptyobject(P): no inequality and no equality rows
  let emptyObj := P.m == 0 && P.me == 0
  -- representsa_emptyObject, type 'hyperplane': res = true
  if emptyObj then true
  -- res = isempty(P.A_.val) && size(P.Ae_.val,1) == 1
  else P.m == 0 && P.me == 1

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
