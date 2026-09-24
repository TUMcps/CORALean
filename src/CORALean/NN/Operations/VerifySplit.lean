import CORALean.NN.Operations.VerifySplitWith
import CORALean.Specification.Operations.Check

/-!
# Verification by recursively splitting the input set, against a specification

`verifySplitWith` at the checker the specification carries: `spec.check`, which asks the
specification's own set about each enclosed output through the representation pair's
`Contains` or `IsDisjoint`. So the caller supplies the specification and the splitter and
no soundness proof for the checker; `Theorems.VerifySplitSound` needs only the splitter's.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m : ℕ}
variable {ContSet : Type} [CORALean.ContSet ContSet (Vec ℝ m)]


-- =====================================  MAIN DEFINITION  ====================================== --

def NeuralNetwork.verifySplit [Contains ContSet (S m)] [IsDisjoint ContSet (S m)]
    (nn : NeuralNetwork S n m) (spec : Specification ContSet)
    (splitter : S n → S n × S n) : ℕ → S n → Bool :=
  nn.verifySplitWith spec.check splitter

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
