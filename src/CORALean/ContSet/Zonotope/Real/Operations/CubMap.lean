module

public import CORALean.ContSet.Zonotope.Real.Operations.CubFold
public import CORALean.ContSet.Zonotope.Real.Operations.CubIdx

@[expose] public section

/-!
# `Zonotope.cubMap`

CORA's `@zonotope/cubMap`: an enclosure of `{ z = (xᵀ T x) * x | x ∈ Z }` by a zonotope,
`zᵢ = Σₖ xₖ · (xᵀ T{i,k} x)`, from the coefficients `Zonotope.cubFold` of the sorted triples of
extended factors. The pure squares `β_k²` of the constant monomial (`listQuad{1}`) are halved
(`β² = 0.5 + 0.5 (2β² - 1)`), half of their sum going into the centre.

The generators are indexed by all ordered triples `(k, j, c)` through `Zonotope.cubIdx`, zero
off `k ≤ j ≤ c` and at `(0, 0, 0)`, which is the centre: `N³` generators where CORA counts
`N (N + 1) (N + 2) / 6 - 1`, the extra ones zero and so the same set, as in `Zonotope.quadMap`.
`ind` (the list of non-zero tensor columns) is not modelled: it defaults to all columns, and a
column left out is the zero matrix.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `aux_cubMapSingle`: the zonotope enclosing `{ (xᵀ T x) * x | x ∈ Z }`. -/
noncomputable def Zonotope.cubMap (T : Fin m → Fin n → Mat ℝ n n) (Z : Zonotope (Vec ℝ n)) :
    Zonotope (Vec ℝ m) where
  h := (Z.h + 1) * (Z.h + 1) * (Z.h + 1)
  -- half the sum of the pure squares of `listQuad{1}` joins the centre
  c := fun i => Z.cubFold T i 0 0 0 + (1 / 2) * ∑ y : Fin Z.h, Z.cubFold T i 0 y.succ y.succ
  G := fun l i =>
    let t := Zonotope.cubIdx (Z.h + 1) (Z.h + 1) (Z.h + 1) l
    if t.1.1 ≤ t.1.2 ∧ t.1.2 ≤ t.2 ∧ ¬(t.1.1 = 0 ∧ t.1.2 = 0 ∧ t.2 = 0) then
      (if t.1.1 = 0 ∧ t.1.2 = t.2 then 1 / 2 else 1) * Z.cubFold T i t.1.1 t.1.2 t.2
    else 0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
