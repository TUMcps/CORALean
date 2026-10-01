import CORALean.NN.Layers.Layer

/-!
# The generator reduction layer

CORA's `nnGeneratorReductionLayer`: the identity on the values, which reduces the set to at most
`maxGens` generators (`aux_reduceGirad`) by the representation's own `reduce`.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `Reduce.reduce` to `maxGens` generators, at every dimension. -/
def Layer.generatorReduction [∀ n, Reduce (S n) (Vec ℝ n)] (n maxGens : ℕ) : Layer S n n where
  enclose s := Reduce.reduce s maxGens

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
