import CORALean.ContDynamics.LinearARX.Operations.InputMat

/-!
# The input signal of the converted system

At step `k` the window moves to `y(k+1..k+p)`, and the input terms of `y(k+p)` are
`∑_j B̄_{j+1} u(k+p-j)`, placed in the last block by `inputMat`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   01-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Scalar

variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] {dy du p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def LinearARX.feed (sys : LinearARX 𝕋 dy du p) (u : ℕ → Vec ℝ du) (k : ℕ) : Vec ℝ (p * dy) :=
  ∑ j : Fin (p + 1), toRealMat (sys.inputMat j) *ᵥ u (k + p - j)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
