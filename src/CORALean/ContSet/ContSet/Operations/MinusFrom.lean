module

public import CORALean.ContSet.ContSet.ContSet
public import CORALean.ContSet.ContSet.Operations.Minus
public import CORALean.ContSet.ContSet.Operations.Uminus
public import CORALean.Global.NegScalar

@[expose] public section

/-!
# CORA's `minus` with a vector minuend

`-S + p`, CORA's second case, where a vector is subtracted from a set the other way round.
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
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, OfPoint (S n) (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `minus` for a numeric minuend `p`: `S = -S + p`. -/
def ContSet.minusFrom (p : Vec ℝ n) (s : S n) : S n :=
  Plus.plus (ContSet.uminus (𝕋 := 𝕋) s) (OfPoint.ofPoint p)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
