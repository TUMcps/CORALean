module

public import CORALean.ContSet.PolyZonotope.Real.Operations.ZonotopeCora

@[expose] public section

/-!
# `PolyZonotope.containsExactCora1D`

`contains(pZ, p, 'exact')` of CORA's `@polyZonotope/contains_.m` for a point `p` and a
one-dimensional `pZ` with a generator (so the centre-only branch, l. 172, is not taken). The
`'exact'` method returns at once into `aux_exactContainment` (ll. 100-102), which asks
`representsa_(pZ,'zonotope',1e-12)` (l. 184). For `n = 1` that answers `true` whatever `pZ`
is (`@polyZonotope/representsa_.m` l. 128: `res = n == 1 || aux_isZonotope(pZ,tol)`), with
`S = zonotope(pZ)`, an outer enclosure only, and `contains_` of that zonotope decides (l. 186).
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The verdict of `contains(pZ, p, 'exact')` for `n = 1`. -/
noncomputable def PolyZonotope.containsExactCora1D (pZ : PolyZonotope (Vec ℝ 1))
    (p : Vec ℝ 1) : Prop :=
  let Z := pZ.zonotopeCora        -- 184. [isZonotope, Z] = representsa_(pZ,'zonotope',1e-12)
  p ∈ Z.construct                 -- 186. contains_(Z,S,method,tol,0,false,false)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
