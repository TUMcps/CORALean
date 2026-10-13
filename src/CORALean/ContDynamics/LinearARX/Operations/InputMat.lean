module

public import CORALean.ContDynamics.LinearARX.LinearARX
public import CORALean.Global.ExactScalar

@[expose] public section

/-!
# The input matrices of the converted system

`B̄_{j+1}` placed in the last block row of the state, the others zero: the lag-`j`
input's contribution to the next window, which enters in state coordinates as
`LinearSysDT`'s input does. CORA's `B_ext{j+1} = E' B̄_{j+1}`, in
`linearARX.setTVP`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   01-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] {dy du p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def LinearARX.inputMat (sys : LinearARX 𝕋 dy du p) (j : Fin (p + 1)) : Mat 𝕋 (p * dy) du :=
  Matrix.of fun r c =>
    if (finProdFinEquiv.symm r).1.val + 1 = p then sys.Bbar j (finProdFinEquiv.symm r).2 c
    else 0

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
