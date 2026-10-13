module

public import CORALean.ContSet.ContSet.ContSet
public import CORALean.Global.NegScalar

@[expose] public section

/-!
# CORA's `uminus`: the negated set

`-1 * S`, as CORA's `uminus` has it, through the set's own `mtimes`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Scalar

variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] [NegScalar 𝕋] {S : ℕ → Type}
variable [∀ n, ContSet (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `uminus`: `S = -1 * S`. -/
def ContSet.uminus (s : S n) : S n :=
  let A : Mat 𝕋 n n := -1
  Mtimes.mtimes A s

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
