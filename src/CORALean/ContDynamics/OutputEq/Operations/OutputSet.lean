module

public import CORALean.ContDynamics.OutputEq.OutputEq

@[expose] public section

/-!
# Output equations: the output set

CORA's `outputSet` without the noise term, `C R ⊕ D U ⊕ k`: `mtimes` twice, `plus` twice and the
offset as a point, operations `LinearSysDT.reach` already runs on, so an output set is computed
wherever a reachable set is, at a float representation included. Nothing here is a scalar
operation of its own, which is why there is no second version of it.

The state and the input are enclosed independently, so every state of `R` is
paired with every input of `U` rather than with the input that occurs at it.
That is the looseness a closed loop already pays, and at `D = 0` it is not paid
at all. CORA's shortcut `Y = R` at `C = 1`, `D = 0`, `k = 0` is not taken: the
set computed is the same, only coarser.
-/

-- Authors:       Claude Sonnet 5, Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar Plus Mtimes

variable {n m r : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S] [OfScalarPoint 𝕋 S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every output the equation produces at a state of `R` under an input of `U`,
enclosed: `C R ⊕ D U ⊕ k`. -/
def OutputEq.outputSet (out : OutputEq 𝕋 n m r) (R : S n) (U : S m) : S r :=
  plus (plus (mtimes out.C R) (mtimes out.D U)) (OfScalarPoint.ofVec out.k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
