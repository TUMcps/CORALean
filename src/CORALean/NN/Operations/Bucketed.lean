import CORALean.Global.Tensor
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic

/-!
# How many neurons the buckets merge

[1, Def. 3]'s buckets are disjoint, so one mask, `true` on a merged neuron, describes them all,
and the count of merged neurons is the mask's count.

## References

* [1] T. Ladner and M. Althoff. "Fully Automatic Neural Network Reduction for
      Formal Verification". TMLR. arXiv:2305.01932.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   23-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `Σ_{B ∈ B_{k,δ}} |B|` for buckets given as one mask, `true` on a merged neuron: the
buckets being disjoint, how many neurons they merge between them. -/
def bucketed {n : ℕ} (B : Fin n → Bool) : ℕ := (Finset.univ.filter fun i => B i = true).card

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
