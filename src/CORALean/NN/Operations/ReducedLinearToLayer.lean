import CORALean.ContSet.Interval.Float.Operations.NonemptyHull
import CORALean.NN.Definitions.ReducibleNetwork
import CORALean.NN.Layers.Operations.LinearWithError

/-!
# The layer [1, Eq. 2] names

`W h + b ⊕ I'`: the generic linear layer carrying the box of errors merging has added, at
`I'.nonemptyHull`, which is what `LinearWithErrorLayer` runs and is `I'` whenever `I'` is
nonempty: the layers [1, Alg. 2] propagates through are then exactly `toNetwork`'s.

## References

* [1] T. Ladner and M. Althoff. "Fully Automatic Neural Network Reduction for
      Formal Verification". TMLR. arXiv:2305.01932.
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]
  {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat 𝕋) S] [Float.IntervalOuter S 𝕋] [Float.OfInterval S 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The layer [1, Eq. 2] names, `W h + b ⊕ I'`. -/
def ReducedLinear.toLayer {n m : ℕ} (L : ReducedLinear 𝕋 n m) : Layer S n m :=
  Layer.linearWithError L.W L.b L.I'.nonemptyHull

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
