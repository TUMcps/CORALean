import CORALean.ContSet.Polygon.Real.Operations.Vertices

/-!
# `Polygon.representsaOriginCora`: the `'origin'` test as CORA's code computes it

CORA's `@polygon/representsa_.m`, branch `'origin'` (l. 63):

```
res = all(withinTol(vertices_(pgon),0,tol),"all");
```

`all` over an empty array is `true`, so a polygon without vertices passes. Here every vertex of
every piece is compared with the origin at tolerance `0`. Read from the source, not run.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

open Classical in
/-- CORA's `res` for `representsa_(pgon, 'origin')`. -/
noncomputable def Polygon.representsaOriginCora (P : Polygon) : Bool :=
  let V := P.vertices                              -- vertices_(pgon)
  V.all fun v => decide (v = 0)                    -- all(withinTol(V,0,tol),"all")

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
