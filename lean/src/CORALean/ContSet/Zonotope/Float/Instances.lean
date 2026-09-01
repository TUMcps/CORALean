import CORALean.ContSet.Zonotope.Float.Theorems.API

/-!
# What `Zonotope` instantiates

The class fields *are* the obligations, so there is nothing to restate.

`ContSet` is not among them: `InflatedContSet` supplies it, which is what makes
this the same class the exact layer instantiates. An algorithm written against
`OuterContSet` therefore runs here with no float counterpart to write.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]

instance {n : ℕ} : OuterContSet (Zonotope 𝕋 n) (Vec ℝ n) where
  plus := Zonotope.plus
  linComb := Zonotope.linComb
  reduce := Zonotope.reduce
  plus_outer := Zonotope.plus_outer
  linComb_outer := Zonotope.linComb_outer
  reduce_outer := Zonotope.reduce_outer

instance : Mtimes (Mat 𝕋) (Zonotope 𝕋) where
  mtimes := Zonotope.mtimes
  mtimes_outer M Z := by
    simp only [ContSet.construct_mat, Set.biUnion_singleton]
    exact Zonotope.mtimes_outer M Z

end CORALean.Float
