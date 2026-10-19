module

public import CORALean.ContDynamics.OutputEq.Operations.OutputSet

@[expose] public section

/-!
# Output equations: the output set with a noise term

CORA's `linearSys.outputSet`, `Y = C R ⊕ D U ⊕ k ⊕ F V`: `OutputSet` for `C R ⊕ D U ⊕ k`, then
the measurement noise `F V`, one more `mtimes` and `plus`. Pass `U` already shifted by
`uTrans`, as CORA forms `U = params.U + params.uTrans`.

Not modelled: the shortcut `Y = R` when `C` is empty (the same set as `C = I`, `D = 0`, `k = 0`,
`F = 0`, which this computes, only coarser), and the optional `reduce` to `saveOrder`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   14-October-2026
-- Reviewed:      19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar Plus Mtimes

variable {n m q r : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S] [OfScalarPoint 𝕋 S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `C R ⊕ D U ⊕ k ⊕ F V`. -/
def OutputEq.outputSetNoise (out : OutputEq 𝕋 n m r) (F : Mat 𝕋 r q)
    (R : S n) (U : S m) (V : S q) : S r :=
  plus (out.outputSet R U) (mtimes F V)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
