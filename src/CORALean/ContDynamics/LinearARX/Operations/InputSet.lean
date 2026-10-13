module

public import CORALean.ContDynamics.LinearARX.Operations.InputMat

@[expose] public section

/-!
# The input set of the converted system

`∑_j E' B̄_{j+1} U`, one `mtimes` per lag and `plus` between them. Every lag draws
from the same `U` but the sum treats the `p+1` draws as independent, which
encloses every ARX input and is where the conversion is looser than the ARX form.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   01-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Scalar Plus Mtimes

variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] {dy du p : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S]


-- =====================================  MAIN DEFINITION  ====================================== --

def LinearARX.inputSet (sys : LinearARX 𝕋 dy du p) (U : S du) : S (p * dy) :=
  (List.finRange p).foldl (fun acc j => plus acc (mtimes (sys.inputMat j.succ) U))
    (mtimes (sys.inputMat 0) U)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
